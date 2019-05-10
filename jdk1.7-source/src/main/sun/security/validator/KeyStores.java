/*
 * Copyright (c) 2002, 2006, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.validator;

import java.io.*;
import java.util.*;

import java.security.*;
import java.security.cert.*;
import java.security.cert.Certificate;

import sun.security.action.*;

/**
 * Collection of static utility methods related to KeyStores.
 *
 * @author Andreas Sterbenz
 */
public class KeyStores {

    private KeyStores() {
        // empty
    }

    // in the future, all accesses to the system cacerts keystore should
    // go through this class. but not right now.
/*
    private final static String javaHome =
        (String)AccessController.doPrivileged(new GetPropertyAction("java.home"));

    private final static char SEP = File.separatorChar;

    private static KeyStore caCerts;

    private static KeyStore getKeyStore(String type, String name,
            char[] password) throws IOException {
        if (type == null) {
            type = "JKS";
        }
        try {
            KeyStore ks = KeyStore.getInstance(type);
            FileInputStream in = (FileInputStream)AccessController.doPrivileged
                                        (new OpenFileInputStreamAction(name));
            ks.load(in, password);
            return ks;
        } catch (GeneralSecurityException e) {
            // XXX
            throw new IOException();
        } catch (PrivilegedActionException e) {
            throw (IOException)e.getCause();
        }
    }

    /**
     * Return a KeyStore with the contents of the lib/security/cacerts file.
     * The file is only opened once per JVM invocation and the contents
     * cached subsequently.
     *
    public synchronized static KeyStore getCaCerts() throws IOException {
        if (caCerts != null) {
            return caCerts;
        }
        String name = javaHome + SEP + "lib" + SEP + "security" + SEP + "cacerts";
        caCerts = getKeyStore(null, name, null);
        return caCerts;
    }
*/

    /**
     * Return a Set with all trusted X509Certificates contained in
     * this KeyStore.
     */
    public static Set<X509Certificate> getTrustedCerts(KeyStore ks) {
        Set<X509Certificate> set = new HashSet<X509Certificate>();
        try {
            for (Enumeration<String> e = ks.aliases(); e.hasMoreElements(); ) {
                String alias = e.nextElement();
                if (ks.isCertificateEntry(alias)) {
                    Certificate cert = ks.getCertificate(alias);
                    if (cert instanceof X509Certificate) {
                        set.add((X509Certificate)cert);
                    }
                } else if (ks.isKeyEntry(alias)) {
                    Certificate[] certs = ks.getCertificateChain(alias);
                    if ((certs != null) && (certs.length > 0) &&
                            (certs[0] instanceof X509Certificate)) {
                        set.add((X509Certificate)certs[0]);
                    }
                }
            }
        } catch (KeyStoreException e) {
            // ignore
        }
        return set;
    }

}
