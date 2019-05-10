/*
 * Copyright (c) 1996, 2010, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.DoubleByte;
import sun.nio.cs.ext.Big5;

/**
 * Tables and data to convert Big5 to Unicode
 *
 */

public class ByteToCharBig5 extends ByteToCharDBCS_ASCII {

    private static DoubleByte.Decoder dec =
        (DoubleByte.Decoder)new Big5().newDecoder();

    public String getCharacterEncoding() {
        return "Big5";
    }

    public ByteToCharBig5() {
        super(dec);
    }
}
