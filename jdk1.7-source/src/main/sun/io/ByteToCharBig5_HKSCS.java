/*
 * Copyright (c) 2001, 2010, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.Big5_HKSCS;
import sun.nio.cs.ext.HKSCS;
import static sun.nio.cs.CharsetMapping.*;

public class ByteToCharBig5_HKSCS extends ByteToCharDBCS_ASCII {

    protected static HKSCS.Decoder dec =
        (HKSCS.Decoder)new Big5_HKSCS().newDecoder();


    public String getCharacterEncoding() {
        return "Big5_HKSCS";
    }

    public ByteToCharBig5_HKSCS() {
        super(dec);
    }

    protected char decodeDouble(int byte1, int byte2) {
        char c = dec.decodeDouble(byte1, byte2);
        if (c == UNMAPPABLE_DECODING)
            c = dec.decodeBig5(byte1, byte2);
        return c;
    }
}
