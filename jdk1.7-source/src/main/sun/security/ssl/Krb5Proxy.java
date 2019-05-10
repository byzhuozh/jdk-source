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
import java.security.Permission;
import java.security.Principal;
import javax.crypto.SecretKey;
import javax.security.auth.Subject;
import javax.security.auth.login.LoginException;

/**
 * An interface to a subset of the Kerberos APIs to avoid a static dependency
 * on the types defined by these APIs.
 */
public interface Krb5Proxy {

    /**
     * Returns the Subject associated with the client-side of the SSL socket.
     */
    Subject getClientSubject(AccessControlContext acc) throws LoginException;

    /**
     * Returns the Subject associated with the server-side of the SSL socket.
     */
    Subject getServerSubject(AccessControlContext acc) throws LoginException;


    /**
     * Returns the KerberosKeys for the default server-side principal.
     */
    SecretKey[] getServerKeys(AccessControlContext acc) throws LoginException;

    /**
     * Returns the server-side principal name associated with the KerberosKey.
     */
    String getServerPrincipalName(SecretKey kerberosKey);

    /**
     * Returns the hostname embedded in the principal name.
     */
    String getPrincipalHostName(Principal principal);

    /**
     * Returns a ServicePermission for the principal name and action.
     */
    Permission getServicePermission(String principalName, String action);
}
