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

public class CharToByteCp930 extends CharToByteDBCS_EBCDIC {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp930";
    }

    public CharToByteCp930() {
        super((DoubleByte.Encoder)new IBM930().newEncoder());
    }
}
