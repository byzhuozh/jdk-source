/*
 * Copyright (c) 2009, 2012, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.ssl.krb5;

import java.security.AccessControlContext;
import java.security.Permission;
import java.security.Principal;
import javax.crypto.SecretKey;
import javax.security.auth.Subject;
import javax.security.auth.kerberos.KerberosKey;
import javax.security.auth.kerberos.ServicePermission;
import javax.security.auth.login.LoginException;

import sun.security.jgss.GSSCaller;
import sun.security.jgss.krb5.Krb5Util;
import sun.security.krb5.PrincipalName;
import sun.security.ssl.Krb5Proxy;

/**
 * An implementation of Krb5Proxy that simply delegates to the appropriate
 * Kerberos APIs.
 */
public class Krb5ProxyImpl implements Krb5Proxy {

    public Krb5ProxyImpl() { }

    @Override
    public Subject getClientSubject(AccessControlContext acc)
            throws LoginException {
        return Krb5Util.getSubject(GSSCaller.CALLER_SSL_CLIENT, acc);
    }

    @Override
    public Subject getServerSubject(AccessControlContext acc)
            throws LoginException {
        return Krb5Util.getSubject(GSSCaller.CALLER_SSL_SERVER, acc);
    }

    @Override
    public SecretKey[] getServerKeys(AccessControlContext acc)
            throws LoginException {
        Krb5Util.ServiceCreds serviceCreds =
            Krb5Util.getServiceCreds(GSSCaller.CALLER_SSL_SERVER, null, acc);
        return serviceCreds != null ? serviceCreds.getKKeys() :
                                        new KerberosKey[0];
    }

    @Override
    public String getServerPrincipalName(SecretKey kerberosKey) {
        return ((KerberosKey)kerberosKey).getPrincipal().getName();
    }

    @Override
    public String getPrincipalHostName(Principal principal) {
        if (principal == null) {
           return null;
        }
        String hostName = null;
        try {
            PrincipalName princName =
                new PrincipalName(principal.getName(),
                        PrincipalName.KRB_NT_SRV_HST);
            String[] nameParts = princName.getNameStrings();
            if (nameParts.length >= 2) {
                hostName = nameParts[1];
            }
        } catch (Exception e) {
            // ignore
        }
        return hostName;
    }


    @Override
    public Permission getServicePermission(String principalName,
            String action) {
        return new ServicePermission(principalName, action);
    }
}
