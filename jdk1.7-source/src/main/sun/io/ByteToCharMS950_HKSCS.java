/*
 * Copyright (c) 2002, 2010, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.HKSCS;
import sun.nio.cs.ext.MS950_HKSCS;
import static sun.nio.cs.CharsetMapping.*;

public class ByteToCharMS950_HKSCS extends ByteToCharDBCS_ASCII {

    private static HKSCS.Decoder dec =
        (HKSCS.Decoder)new MS950_HKSCS().newDecoder();

    public String getCharacterEncoding() {
        return "MS950_HKSCS";
    }

    public ByteToCharMS950_HKSCS() {
        super(dec);
    }

    protected char decodeDouble(int byte1, int byte2) {
        char c = dec.decodeDouble(byte1, byte2);
        if (c == UNMAPPABLE_DECODING)
            c = dec.decodeBig5(byte1, byte2);
        return c;
    }
}
