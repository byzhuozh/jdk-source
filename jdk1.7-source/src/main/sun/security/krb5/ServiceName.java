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
 *
 *  (C) Copyright IBM Corp. 1999 All Rights Reserved.
 *  Copyright 1997 The Open Group Research Institute.  All rights reserved.
 */

package sun.security.krb5;

import java.net.InetAddress;
import java.net.UnknownHostException;

public class ServiceName extends PrincipalName {

    public ServiceName(String name, int type) throws RealmException {
        super(name, type);

    }
    public ServiceName(String name) throws RealmException {
        this(name, PrincipalName.KRB_NT_UNKNOWN);
    }

    public ServiceName(String name, String realm) throws RealmException {
        this(name, PrincipalName.KRB_NT_UNKNOWN);
        setRealm(realm);
    }

    public ServiceName (String service, String instance, String realm)
        throws KrbException
    {
        super(service, instance, realm, PrincipalName.KRB_NT_SRV_INST);
    }

}
