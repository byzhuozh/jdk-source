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

public class CharToByteCp935 extends CharToByteDBCS_EBCDIC {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp935";
    }

    public CharToByteCp935() {
        super((DoubleByte.Encoder)new IBM935().newEncoder());
    }
}
