/*
 * Copyright (c) 2011, Oracle and/or its affiliates. All rights reserved.
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

package sun.misc;

import javax.security.auth.kerberos.KeyTab;
import sun.security.krb5.EncryptionKey;
import sun.security.krb5.PrincipalName;

/**
 * An unsafe tunnel to get non-public access to classes in the
 * javax.security.auth.kerberos package.
 */
public interface JavaxSecurityAuthKerberosAccess {
    /**
     * Returns keys for a principal in a keytab.
     * @return the keys, never null, can be empty.
     */
    public EncryptionKey[] keyTabGetEncryptionKeys(
            KeyTab ktab, PrincipalName principal);
}
