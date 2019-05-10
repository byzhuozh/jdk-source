/*
 * Copyright (c) 2009, 2010, Oracle and/or its affiliates. All rights reserved.
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

import java.security.AccessControlContext;
import java.security.AccessController;
import java.security.Permission;
import java.security.Principal;
import java.security.PrivilegedAction;
import javax.crypto.SecretKey;
import javax.security.auth.Subject;
import javax.security.auth.login.LoginException;

/**
 * A helper class for Kerberos APIs.
 */
public final class Krb5Helper {

    private Krb5Helper() { }

    // loads Krb5Proxy implementation class if available
    private static final String IMPL_CLASS =
        "sun.security.ssl.krb5.Krb5ProxyImpl";

    private static final Krb5Proxy proxy =
        AccessController.doPrivileged(new PrivilegedAction<Krb5Proxy>() {
            public Krb5Proxy run() {
                try {
                    Class<?> c = Class.forName(IMPL_CLASS, true, null);
                    return (Krb5Proxy)c.newInstance();
                } catch (ClassNotFoundException cnf) {
                    return null;
                } catch (InstantiationException e) {
                    throw new AssertionError(e);
                } catch (IllegalAccessException e) {
                    throw new AssertionError(e);
                }
            }});

    /**
     * Returns true if Kerberos is available.
     */
    public static boolean isAvailable() {
        return proxy != null;
    }

    private static void ensureAvailable() {
        if (proxy == null)
            throw new AssertionError("Kerberos should have been available");
    }

    /**
     * Returns the Subject associated with client-side of the SSL socket.
     */
    public static Subject getClientSubject(AccessControlContext acc)
            throws LoginException {
        ensureAvailable();
        return proxy.getClientSubject(acc);
    }

    /**
     * Returns the Subject associated with server-side of the SSL socket.
     */
    public static Subject getServerSubject(AccessControlContext acc)
            throws LoginException {
        ensureAvailable();
        return proxy.getServerSubject(acc);
    }

    /**
     * Returns the KerberosKeys for the default server-side principal.
     */
    public static SecretKey[] getServerKeys(AccessControlContext acc)
            throws LoginException {
        ensureAvailable();
        return proxy.getServerKeys(acc);
    }

    /**
     * Returns the server-side principal name associated with the KerberosKey.
     */
    public static String getServerPrincipalName(SecretKey kerberosKey) {
        ensureAvailable();
        return proxy.getServerPrincipalName(kerberosKey);
    }

    /**
     * Returns the hostname embedded in the principal name.
     */
    public static String getPrincipalHostName(Principal principal) {
        ensureAvailable();
        return proxy.getPrincipalHostName(principal);
    }

    /**
     * Returns a ServicePermission for the principal name and action.
     */
    public static Permission getServicePermission(String principalName,
            String action) {
        ensureAvailable();
        return proxy.getServicePermission(principalName, action);
    }
}
