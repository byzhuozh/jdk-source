/*
 * Copyright (c) 1997, 1998, Oracle and/or its affiliates. All rights reserved.
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

public class CharToByteMS932 extends CharToByteDBCS_ASCII {

    private static DoubleByte.Encoder enc =
        (DoubleByte.Encoder)new MS932().newEncoder();

    public String getCharacterEncoding() {
        return "MS932";
    }

    public CharToByteMS932() {
        super(enc);
    }
}
