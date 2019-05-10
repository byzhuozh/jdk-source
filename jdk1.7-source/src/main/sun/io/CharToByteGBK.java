/*
 * Copyright (c) 1997, 2003, Oracle and/or its affiliates. All rights reserved.
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

public class CharToByteGBK extends CharToByteDBCS_ASCII {

    private static DoubleByte.Encoder enc =
        (DoubleByte.Encoder)new GBK().newEncoder();

    public String getCharacterEncoding() {
        return "GBK";
    }

    public CharToByteGBK() {
        super(enc);
    }
}
