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

package sun.security.krb5;

public class RealmException extends KrbException {

    private static final long serialVersionUID = -9100385213693792864L;

    public RealmException(int i) {
        super(i);
    }

    public RealmException(String s) {
        super(s);
    }

    public RealmException(int i, String s) {
        super(i,s);
    }

}
