/*
 * Copyright (c) 2000, 2003, Oracle and/or its affiliates. All rights reserved.
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

public class KrbApErrException extends sun.security.krb5.KrbException {

    private static final long serialVersionUID = 7545264413323118315L;

    public KrbApErrException(int i) {
        super(i);
    }

    public KrbApErrException(int i, String s) {
        super(i, s);
    }

}
