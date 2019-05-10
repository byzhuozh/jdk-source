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

public class ByteToCharJohab extends ByteToCharDBCS_ASCII {

    private static DoubleByte.Decoder dec =
        (DoubleByte.Decoder)new Johab().newDecoder();

    public String getCharacterEncoding() {
        return "Johab";
    }

    public ByteToCharJohab() {
        super(dec);
    }
}
