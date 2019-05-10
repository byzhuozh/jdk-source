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

public class CharToByteCp942C extends CharToByteDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp942C";
    }

    public CharToByteCp942C() {
        super((DoubleByte.Encoder)new IBM942C().newEncoder());
    }
}
