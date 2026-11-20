//! Append-only files that a crash, or a failed write, can never corrupt beyond their unacknowledged end.
use anyhow::{Context, Result};
use std::fs::{File, OpenOptions};
use std::io::Write;

pub struct AppendFile {
    file: File,
    /// The length of what was acknowledged.
    len: u64,
    /// Whether a failed append's bytes may still follow `len`: an append after them would land shifted.
    torn: bool,
}

impl AppendFile {
    /// Opens `path`, creating it, and returns its contents cut to the length `valid` accepts. The rest was torn by a
    /// crash and never acknowledged, so it is dropped from the file too.
    pub fn open(path: &str, valid: impl Fn(&[u8]) -> usize) -> Result<(Self, Vec<u8>)> {
        let mut data = match std::fs::read(path) {
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Vec::new(),
            r => r?,
        };
        let file = OpenOptions::new().create(true).append(true).open(path)?;
        let n = valid(&data);
        if n < data.len() {
            tracing::warn!(
                path,
                dropped = data.len() - n,
                "dropping bytes torn by a crash"
            );
            file.set_len(n as u64)?;
            file.sync_all()?;
            data.truncate(n);
        }
        let len = n as u64;
        Ok((
            Self {
                file,
                len,
                torn: false,
            },
            data,
        ))
    }

    /// Appends `bytes` durably, or leaves the file as it was: an append after half a write would land shifted, or join
    /// a torn line and be lost with it. A failed append that cannot be cut off at once is cut off before the next one,
    /// which fails for as long as it cannot.
    pub fn append(&mut self, bytes: &[u8]) -> Result<()> {
        if self.torn {
            self.file
                .set_len(self.len)
                .context("cutting off a failed append")?;
            self.torn = false;
        }
        if let Err(e) = self
            .file
            .write_all(bytes)
            .and_then(|()| self.file.sync_data())
        {
            self.torn = self.file.set_len(self.len).is_err();
            return Err(e.into());
        }
        self.len += bytes.len() as u64;
        Ok(())
    }
}

/// For [`AppendFile::open`] on a file of lines: everything up to the last newline.
pub fn whole_lines(data: &[u8]) -> usize {
    data.iter().rposition(|&b| b == b'\n').map_or(0, |i| i + 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_torn_end_is_cut_and_appending_resumes() {
        let path = std::env::temp_dir().join(format!("common-append-{}", std::process::id()));
        let path = path.to_str().unwrap();
        let _ = std::fs::remove_file(path);
        let (mut f, data) = AppendFile::open(path, whole_lines).unwrap();
        assert!(data.is_empty());
        f.append(b"a\nb\n").unwrap();
        f.file.write_all(b"torn").unwrap(); // a crash mid-line
        drop(f);
        let (mut f, data) = AppendFile::open(path, whole_lines).unwrap();
        assert_eq!(data, b"a\nb\n");
        f.append(b"c\n").unwrap();
        drop(f);
        assert_eq!(std::fs::read(path).unwrap(), b"a\nb\nc\n");
        std::fs::remove_file(path).unwrap();
    }
}
