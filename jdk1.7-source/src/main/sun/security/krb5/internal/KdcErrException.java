/*
 * Copyright (c) 2000, 2004, Oracle and/or its affiliates. All rights reserved.
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

public class KdcErrException extends sun.security.krb5.KrbException {

    private static final long serialVersionUID = -8788186031117310306L;

    public KdcErrException(int i) {
        super(i);
    }

    public KdcErrException(int i, String s) {
        super(i, s);
    }
}
