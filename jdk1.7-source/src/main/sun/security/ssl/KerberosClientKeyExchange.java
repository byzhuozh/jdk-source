/*
 * Copyright (c) 2003, 2010, Oracle and/or its affiliates. All rights reserved.
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
import java.security.AccessController;
import java.security.AccessControlContext;
import java.security.Principal;
import java.security.PrivilegedAction;
import java.security.SecureRandom;
import javax.crypto.SecretKey;

/**
 * A helper class that calls the KerberosClientKeyExchange implementation.
 */
public class KerberosClientKeyExchange extends HandshakeMessage {

    private static final String IMPL_CLASS =
        "sun.security.ssl.krb5.KerberosClientKeyExchangeImpl";

    private static final Class<?> implClass = AccessController.doPrivileged(
            new PrivilegedAction<Class<?>>() {
                public Class<?> run() {
                    try {
                        return Class.forName(IMPL_CLASS, true, null);
                    } catch (ClassNotFoundException cnf) {
                        return null;
                    }
                }
            }
        );
    private final KerberosClientKeyExchange impl = createImpl();

    private KerberosClientKeyExchange createImpl() {
        if (getClass() == KerberosClientKeyExchange.class) {
            try {
                return (KerberosClientKeyExchange)implClass.newInstance();
            } catch (InstantiationException e) {
                throw new AssertionError(e);
            } catch (IllegalAccessException e) {
                throw new AssertionError(e);
            }
        }
        return null;
    }

    public KerberosClientKeyExchange() {
        // empty
    }

    public KerberosClientKeyExchange(String serverName, boolean isLoopback,
        AccessControlContext acc, ProtocolVersion protocolVersion,
        SecureRandom rand) throws IOException {

        if (impl != null) {
            init(serverName, isLoopback, acc, protocolVersion, rand);
        } else {
            throw new IllegalStateException("Kerberos is unavailable");
        }
    }

    public KerberosClientKeyExchange(ProtocolVersion protocolVersion,
        ProtocolVersion clientVersion, SecureRandom rand,
        HandshakeInStream input, SecretKey[] serverKeys) throws IOException {

        if (impl != null) {
            init(protocolVersion, clientVersion, rand, input, serverKeys);
        } else {
            throw new IllegalStateException("Kerberos is unavailable");
        }
    }

    @Override
    int messageType() {
        return ht_client_key_exchange;
    }

    @Override
    public int  messageLength() {
        return impl.messageLength();
    }

    @Override
    public void send(HandshakeOutStream s) throws IOException {
        impl.send(s);
    }

    @Override
    public void print(PrintStream p) throws IOException {
        impl.print(p);
    }

    public void init(String serverName, boolean isLoopback,
        AccessControlContext acc, ProtocolVersion protocolVersion,
        SecureRandom rand) throws IOException {

        if (impl != null) {
            impl.init(serverName, isLoopback, acc, protocolVersion, rand);
        }
    }

    public void init(ProtocolVersion protocolVersion,
        ProtocolVersion clientVersion, SecureRandom rand,
        HandshakeInStream input, SecretKey[] serverKeys) throws IOException {

        if (impl != null) {
            impl.init(protocolVersion, clientVersion, rand, input, serverKeys);
        }
    }

    public byte[] getUnencryptedPreMasterSecret() {
        return impl.getUnencryptedPreMasterSecret();
    }

    public Principal getPeerPrincipal(){
        return impl.getPeerPrincipal();
    }

    public Principal getLocalPrincipal(){
        return impl.getLocalPrincipal();
    }
}
