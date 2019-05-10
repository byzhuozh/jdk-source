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

import java.io.IOException;
import java.io.PrintStream;

import java.security.PublicKey;
import java.security.interfaces.ECPublicKey;
import java.security.spec.*;

/**
 * ClientKeyExchange message for all ECDH based key exchange methods. It
 * contains the client's ephemeral public value.
 *
 * @since   1.6
 * @author  Andreas Sterbenz
 */
final class ECDHClientKeyExchange extends HandshakeMessage {

    int messageType() {
        return ht_client_key_exchange;
    }

    private byte[] encodedPoint;

    byte[] getEncodedPoint() {
        return encodedPoint;
    }

    // Called by the client with its ephemeral public key.
    ECDHClientKeyExchange(PublicKey publicKey) {
        ECPublicKey ecKey = (ECPublicKey)publicKey;
        ECPoint point = ecKey.getW();
        ECParameterSpec params = ecKey.getParams();
        encodedPoint = JsseJce.encodePoint(point, params.getCurve());
    }

    ECDHClientKeyExchange(HandshakeInStream input) throws IOException {
        encodedPoint = input.getBytes8();
    }

    int messageLength() {
        return encodedPoint.length + 1;
    }

    void send(HandshakeOutStream s) throws IOException {
        s.putBytes8(encodedPoint);
    }

    void print(PrintStream s) throws IOException {
        s.println("*** ECDHClientKeyExchange");

        if (debug != null && Debug.isOn("verbose")) {
            Debug.println(s, "ECDH Public value", encodedPoint);
        }
    }
}
