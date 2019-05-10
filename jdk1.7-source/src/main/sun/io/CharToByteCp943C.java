/*
 * Copyright (c) 1997, Oracle and/or its affiliates. All rights reserved.
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

public class CharToByteCp943C extends CharToByteDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp943C";
    }

    public CharToByteCp943C() {
        super((DoubleByte.Encoder)new IBM943C().newEncoder());
    }
}
