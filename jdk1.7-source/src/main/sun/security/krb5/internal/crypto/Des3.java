/*
 * Copyright (c) 2004, 2007, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */


package sun.security.krb5.internal.crypto;

import sun.security.krb5.internal.crypto.dk.Des3DkCrypto;
import sun.security.krb5.KrbCryptoException;
import java.security.GeneralSecurityException;

/**
 * Class with static methods for doing Triple DES operations.
 */
public class Des3 {
    private static final Des3DkCrypto CRYPTO = new Des3DkCrypto();

    private Des3() {
    }

    public static byte[] stringToKey(char[] chars)
        throws GeneralSecurityException {
        return CRYPTO.stringToKey(chars);
    }

    public static byte[] parityFix(byte[] value)
        throws GeneralSecurityException {
        return CRYPTO.parityFix(value);
    }

    // in bytes
    public static int getChecksumLength() {
        return CRYPTO.getChecksumLength();
    }

    public static byte[] calculateChecksum(byte[] baseKey, int usage,
        byte[] input, int start, int len) throws GeneralSecurityException {
            return CRYPTO.calculateChecksum(baseKey, usage, input, start, len);
    }

    public static byte[] encrypt(byte[] baseKey, int usage,
        byte[] ivec, byte[] plaintext, int start, int len)
        throws GeneralSecurityException, KrbCryptoException {
            return CRYPTO.encrypt(baseKey, usage, ivec, null /* new_ivec */,
                plaintext, start, len);
    }

    /* Encrypt plaintext; do not add confounder, padding, or checksum */
    public static byte[] encryptRaw(byte[] baseKey, int usage,
        byte[] ivec, byte[] plaintext, int start, int len)
        throws GeneralSecurityException, KrbCryptoException {
        return CRYPTO.encryptRaw(baseKey, usage, ivec, plaintext, start, len);
    }

    public static byte[] decrypt(byte[] baseKey, int usage, byte[] ivec,
        byte[] ciphertext, int start, int len)
        throws GeneralSecurityException {
        return CRYPTO.decrypt(baseKey, usage, ivec, ciphertext, start, len);
    }

    /**
     * Decrypt ciphertext; do not remove confounder, padding,
     * or check checksum
     */
    public static byte[] decryptRaw(byte[] baseKey, int usage, byte[] ivec,
        byte[] ciphertext, int start, int len)
        throws GeneralSecurityException {
        return CRYPTO.decryptRaw(baseKey, usage, ivec, ciphertext, start, len);
    }
};
