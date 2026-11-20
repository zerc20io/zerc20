import { BaseError, UserRejectedRequestError } from 'viem';
import { expect, test } from 'vitest';
import { guard } from '../src/errors.js';

test('a declined prompt is user-rejected, also wrapped as viem wraps a transaction', async () => {
  const declined = new UserRejectedRequestError(new Error('no'));
  await expect(guard(Promise.reject(declined))).rejects.toMatchObject({ code: 'user-rejected' });
  await expect(guard(Promise.reject(new BaseError('execution reverted', { cause: declined })))).rejects.toMatchObject({
    code: 'user-rejected',
  });
  await expect(guard(Promise.reject({ code: 4001 }))).rejects.toMatchObject({ code: 'user-rejected' });
  await expect(guard(Promise.reject(new Error('rpc down')))).rejects.toThrow('rpc down');
});
