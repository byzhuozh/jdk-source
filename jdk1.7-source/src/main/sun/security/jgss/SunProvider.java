/*
 * Copyright (c) 2000, 2006, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.jgss;

import java.security.Provider;
import java.security.AccessController;

/**
 * Defines the Sun JGSS provider.
 * Will merger this with the Sun security provider
 * sun.security.provider.Sun when the JGSS src is merged with the JDK
 * src.
 *
 * Mechanisms supported are:
 *
 * - Kerberos v5 as defined in RFC 1964.
 *   Oid is 1.2.840.113554.1.2.2
 *
 * - SPNEGO as defined in RFC 2478
 *   Oid is 1.3.6.1.5.5.2
 *
 *   [Dummy mechanism is no longer compiled:
 * - Dummy mechanism. This is primarily useful to test a multi-mech
 *   environment.
 *   Oid is 1.3.6.1.4.1.42.2.26.1.2]
 *
 * @author Mayank Upadhyay
 */

public final class SunProvider extends Provider {

    private static final long serialVersionUID = -238911724858694198L;

    private static final String INFO = "Sun " +
        "(Kerberos v5, SPNEGO)";
    //  "(Kerberos v5, Dummy GSS-API Mechanism)";

    public static final SunProvider INSTANCE = new SunProvider();

    public SunProvider() {
        /* We are the Sun JGSS provider */
        super("SunJGSS", 1.7d, INFO);

        AccessController.doPrivileged(
                        new java.security.PrivilegedAction<Void>() {
            public Void run() {
                put("GssApiMechanism.1.2.840.113554.1.2.2",
                    "sun.security.jgss.krb5.Krb5MechFactory");
                put("GssApiMechanism.1.3.6.1.5.5.2",
                    "sun.security.jgss.spnego.SpNegoMechFactory");
                /*
                  put("GssApiMechanism.1.3.6.1.4.1.42.2.26.1.2",
                  "sun.security.jgss.dummy.DummyMechFactory");
                */
                return null;
            }
        });
    }
}
