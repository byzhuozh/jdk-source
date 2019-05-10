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

// EUC_Simple is the same as DBCS_ASCII
public class CharToByteCp970 extends CharToByteDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp970";
    }

    public CharToByteCp970() {
        super((DoubleByte.Encoder)new IBM970().newEncoder());
    }
}
