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

public class CharToByteCp1381 extends CharToByteDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp1381";
    }

    public CharToByteCp1381() {
        super((DoubleByte.Encoder)new IBM1381().newEncoder());
    }
}
