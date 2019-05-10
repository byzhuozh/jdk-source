/*
 * Copyright (c) 2001, 2007, Oracle and/or its affiliates. All rights reserved.
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

import java.security.SecureRandom;

public final class Confounder {
    private static SecureRandom srand = new SecureRandom();

    private Confounder() { // not instantiable
    }

    public static byte[] bytes(int size) {
        byte[] data = new byte[size];
        srand.nextBytes(data);
        return data;
    }

    public static int intValue() {
        return srand.nextInt();
    }

    public static long longValue() {
        return srand.nextLong();
    }
}
