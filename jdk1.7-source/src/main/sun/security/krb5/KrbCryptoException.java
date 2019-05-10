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

/**
 * KrbCryptoExceptoin is a wrapper exception for exceptions thrown by JCE.
 *
 * @author Yanni Zhang
 */
public class KrbCryptoException extends KrbException {

    private static final long serialVersionUID = -1657367919979982250L;

    public KrbCryptoException (String s) {
        super(s);
    }
}
