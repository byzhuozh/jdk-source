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

package sun.security.krb5.internal;

public class KrbErrException extends sun.security.krb5.KrbException {

    private static final long serialVersionUID = 2186533836785448317L;

    public KrbErrException(int i) {
        super(i);
    }

    public KrbErrException(int i, String s) {
        super(i, s);
    }

}
