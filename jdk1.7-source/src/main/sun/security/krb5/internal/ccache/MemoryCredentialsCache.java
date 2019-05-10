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

package sun.security.krb5.internal.ccache;

import sun.security.krb5.*;
import sun.security.krb5.internal.*;
import java.io.IOException;
import java.io.File;

//Windows supports the "API: cache" type, which is a shared memory cache.  This is
//implemented by krbcc32.dll as part of the MIT Kerberos for Win32 distribution.
//MemoryCredentialsCache will provide future functions to access shared memeory cache on
//Windows platform. Native code implementation may be necessary.
/**
 * This class extends CredentialsCache. It is used for accessing data in shared memory
 * cache on Windows platforms.
 *
 * @author Yanni Zhang
 */
public abstract class MemoryCredentialsCache extends CredentialsCache {

    private static CredentialsCache getCCacheInstance(PrincipalName p) {
        return null;
    }

    private static CredentialsCache getCCacheInstance(PrincipalName p, File cacheFile) {
        return null;
    }


    public abstract boolean exists(String cache);

    public abstract void update(Credentials c);

    public abstract void save() throws IOException, KrbException;

    public abstract Credentials[] getCredsList();

    public abstract Credentials getCreds(PrincipalName sname, Realm srealm) ;

    public abstract PrincipalName getPrimaryPrincipal();

}
