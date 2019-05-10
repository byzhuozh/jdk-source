/*
 * Copyright (c) 1998, 2003, Oracle and/or its affiliates. All rights reserved.
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


package sun.io;

import sun.nio.cs.ext.*;

public class CharToByteMS949 extends CharToByteDBCS_ASCII {

    private static DoubleByte.Encoder enc =
        (DoubleByte.Encoder)new MS949().newEncoder();

    public String getCharacterEncoding() {
        return "MS949";
    }

    public CharToByteMS949() {
        super(enc);
    }
}
