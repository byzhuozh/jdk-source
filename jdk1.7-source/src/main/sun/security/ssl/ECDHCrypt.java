/*
 * Copyright (c) 2006, 2007, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.ssl;

import java.security.*;
import java.security.interfaces.ECPublicKey;
import java.security.spec.*;

import javax.crypto.SecretKey;
import javax.crypto.KeyAgreement;
import javax.crypto.spec.*;

/**
 * Helper class for the ECDH key exchange. It generates the appropriate
 * ephemeral keys as necessary and performs the actual shared secret derivation.
 *
 * @since   1.6
 * @author  Andreas Sterbenz
 */
final class ECDHCrypt {

    // our private key
    private PrivateKey privateKey;

    // our public key
    private ECPublicKey publicKey;

    // Called by ServerHandshaker for static ECDH
    ECDHCrypt(PrivateKey privateKey, PublicKey publicKey) {
        this.privateKey = privateKey;
        this.publicKey = (ECPublicKey)publicKey;
    }

    // Called by ServerHandshaker for ephemeral ECDH
    ECDHCrypt(String curveName, SecureRandom random) {
        try {
            KeyPairGenerator kpg = JsseJce.getKeyPairGenerator("EC");
            ECGenParameterSpec params = new ECGenParameterSpec(curveName);
            kpg.initialize(params, random);
            KeyPair kp = kpg.generateKeyPair();
            privateKey = kp.getPrivate();
            publicKey = (ECPublicKey)kp.getPublic();
        } catch (GeneralSecurityException e) {
            throw new RuntimeException("Could not generate DH keypair", e);
        }
    }

    // Called by ClientHandshaker with params it received from the server
    ECDHCrypt(ECParameterSpec params, SecureRandom random) {
        try {
            KeyPairGenerator kpg = JsseJce.getKeyPairGenerator("EC");
            kpg.initialize(params, random);
            KeyPair kp = kpg.generateKeyPair();
            privateKey = kp.getPrivate();
            publicKey = (ECPublicKey)kp.getPublic();
        } catch (GeneralSecurityException e) {
            throw new RuntimeException("Could not generate DH keypair", e);
        }
    }

    /**
     * Gets the public key of this end of the key exchange.
     */
    PublicKey getPublicKey() {
        return publicKey;
    }

    // called by ClientHandshaker with either the server's static or ephemeral public key
    SecretKey getAgreedSecret(PublicKey peerPublicKey) {
        try {
            KeyAgreement ka = JsseJce.getKeyAgreement("ECDH");
            ka.init(privateKey);
            ka.doPhase(peerPublicKey, true);
            return ka.generateSecret("TlsPremasterSecret");
        } catch (GeneralSecurityException e) {
            throw new RuntimeException("Could not generate secret", e);
        }
    }

    // called by ServerHandshaker
    SecretKey getAgreedSecret(byte[] encodedPoint) {
        try {
            ECParameterSpec params = publicKey.getParams();
            ECPoint point = JsseJce.decodePoint(encodedPoint, params.getCurve());
            KeyFactory kf = JsseJce.getKeyFactory("EC");
            ECPublicKeySpec spec = new ECPublicKeySpec(point, params);
            PublicKey peerPublicKey = kf.generatePublic(spec);
            return getAgreedSecret(peerPublicKey);
        } catch (GeneralSecurityException e) {
            throw new RuntimeException("Could not generate secret", e);
        } catch (java.io.IOException e) {
            throw new RuntimeException("Could not generate secret", e);
        }
    }

}
