/*
 * Copyright (c) 2004, Oracle and/or its affiliates. All rights reserved.
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

import sun.security.krb5.Checksum;
import sun.security.krb5.KrbCryptoException;
import sun.security.krb5.internal.*;
import javax.crypto.spec.DESKeySpec;
import java.security.InvalidKeyException;
import java.security.GeneralSecurityException;

/*
 * This class encapsulates the checksum type for AES128
 *
 * @author Seema Malkani
 */

public class HmacSha1Aes128CksumType extends CksumType {

    public HmacSha1Aes128CksumType() {
    }

    public int confounderSize() {
        return 16;
    }

    public int cksumType() {
        return Checksum.CKSUMTYPE_HMAC_SHA1_96_AES128;
    }

    public boolean isSafe() {
        return true;
    }

    public int cksumSize() {
        return 12;  // bytes
    }

    public int keyType() {
        return Krb5.KEYTYPE_AES;
    }

    public int keySize() {
        return 16;   // bytes
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
     */
    public byte[] calculateKeyedChecksum(byte[] data, int size, byte[] key,
        int usage) throws KrbCryptoException {

         try {
            return Aes128.calculateChecksum(key, usage, data, 0, size);
         } catch (GeneralSecurityException e) {
            KrbCryptoException ke = new KrbCryptoException(e.getMessage());
            ke.initCause(e);
            throw ke;
         }
    }

    /**
     * Verifies keyed checksum.
     * @param data the data.
     * @param size the length of data.
     * @param key the key used to encrypt the checksum.
     * @param checksum
     * @return true if verification is successful.
     */
    public boolean verifyKeyedChecksum(byte[] data, int size,
        byte[] key, byte[] checksum, int usage) throws KrbCryptoException {

         try {
            byte[] newCksum = Aes128.calculateChecksum(key, usage,
                                                        data, 0, size);
            return isChecksumEqual(checksum, newCksum);
         } catch (GeneralSecurityException e) {
            KrbCryptoException ke = new KrbCryptoException(e.getMessage());
            ke.initCause(e);
            throw ke;
         }
    }
}
