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

import sun.nio.cs.ext.DoubleByte;
import sun.nio.cs.ext.Big5_Solaris;

public class ByteToCharBig5_Solaris extends ByteToCharDBCS_ASCII {

    private static DoubleByte.Decoder dec =
        (DoubleByte.Decoder)new Big5_Solaris().newDecoder();

    public String getCharacterEncoding() {
        return "Big5_Solaris";
    }

    public ByteToCharBig5_Solaris() {
        super(dec);
    }
}
