/*
 * Copyright (c) 1997, 1998, Oracle and/or its affiliates. All rights reserved.
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

public class ByteToCharMS932 extends ByteToCharDBCS_ASCII {

    private static DoubleByte.Decoder dec =
        (DoubleByte.Decoder)new MS932().newDecoder();

    public String getCharacterEncoding() {
        return "MS932";
    }

    public ByteToCharMS932() {
        super(dec);
    }

}
