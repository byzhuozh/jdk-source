/*
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

/*
 *  (C) Copyright IBM Corp. 1999 All Rights Reserved.
 *  Copyright 1997 The Open Group Research Institute.  All rights reserved.
 */

package sun.security.krb5.internal.crypto;

import sun.security.krb5.Checksum;
import sun.security.krb5.EncryptedData;
import sun.security.krb5.internal.*;

public class NullEType extends EType {

    public NullEType() {
    }

    public int eType() {
        return EncryptedData.ETYPE_NULL;
    }

    public int minimumPadSize() {
        return 0;
    }

    public int confounderSize() {
        return 0;
    }

    public int checksumType() {
        return Checksum.CKSUMTYPE_NULL;
    }

    public int checksumSize() {
        return 0;
    }

    public int blockSize() {
        return 1;
    }

    public int keyType() {
        return Krb5.KEYTYPE_NULL;
    }

    public int keySize() {
        return 0;
    }

    public byte[] encrypt(byte[] data, byte[] key, int usage) {
        byte[] cipher = new byte[data.length];
        System.arraycopy(data, 0, cipher, 0, data.length);
        return cipher;
    }

    public byte[] encrypt(byte[] data, byte[] key, byte[] ivec, int usage) {
        byte[] cipher = new byte[data.length];
        System.arraycopy(data, 0, cipher, 0, data.length);
        return cipher;
    }

    public byte[] decrypt(byte[] cipher, byte[] key, int usage)
        throws KrbApErrException {
            return cipher.clone();
    }

    public byte[] decrypt(byte[] cipher, byte[] key, byte[] ivec, int usage)
        throws KrbApErrException {
            return cipher.clone();
    }
}
