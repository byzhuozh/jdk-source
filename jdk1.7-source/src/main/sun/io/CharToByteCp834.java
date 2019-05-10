/*
 * Copyright (c) 2006, Oracle and/or its affiliates. All rights reserved.
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

//EBIDIC DBCSONLY Korean

public class CharToByteCp834 extends CharToByteDBCS_ASCII {

    public CharToByteCp834() {
       super((DoubleByte.Encoder)new IBM834().newEncoder());
       subBytes = new byte[] {(byte)0xfe, (byte)0xfe};
    }

    public int getMaxBytesPerChar() {
       return 2;
    }

    public String getCharacterEncoding() {
       return "Cp834";
    }
}
