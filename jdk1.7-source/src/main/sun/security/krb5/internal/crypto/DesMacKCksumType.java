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
import sun.security.krb5.KrbCryptoException;
import sun.security.krb5.internal.*;
import javax.crypto.spec.DESKeySpec;
import java.security.InvalidKeyException;

public class DesMacKCksumType extends CksumType {

    public DesMacKCksumType() {
    }

    public int confounderSize() {
        return 0;
    }

    public int cksumType() {
        return Checksum.CKSUMTYPE_DES_MAC_K;
    }

    public boolean isSafe() {
        return true;
    }

    public int cksumSize() {
        return 16;
    }

    public int keyType() {
        return Krb5.KEYTYPE_DES;
    }

    public int keySize() {
        return 8;
    }

    public byte[] calculateChecksum(byte[] data, int size) {
        return null;
    }

    /**
     * Calculates keyed checksum.
     * @param data the data used to generate the checksum.
     * @param size length of the data.
     * @param key the key used to encrypt the checksum.
     * @return keyed checksum.
     *
     * @modified by Yanni Zhang, 12/08/99.
     */
    public byte[] calculateKeyedChecksum(byte[] data, int size, byte[] key,
        int usage) throws KrbCryptoException {
        //check for weak keys
        try {
            if (DESKeySpec.isWeak(key, 0)) {
                key[7] = (byte)(key[7] ^ 0xF0);
            }
        } catch (InvalidKeyException ex) {
            // swallow, since it should never happen
        }
        byte[] ivec = new byte[key.length];
        System.arraycopy(key, 0, ivec, 0, key.length);
        byte[] cksum = Des.des_cksum(ivec, data, key);
        return cksum;
    }

    public boolean verifyKeyedChecksum(byte[] data, int size,
        byte[] key, byte[] checksum, int usage) throws KrbCryptoException {
        byte[] new_cksum = calculateKeyedChecksum(data, data.length, key, usage);
        return isChecksumEqual(checksum, new_cksum);
    }

}
