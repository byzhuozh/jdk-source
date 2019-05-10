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
import sun.nio.cs.ext.Big5_HKSCS;

public class CharToByteBig5_HKSCS extends CharToByteDBCS_ASCII {
    private static DoubleByte.Encoder enc =
        (DoubleByte.Encoder)new Big5_HKSCS().newEncoder();

    public String getCharacterEncoding() {
        return "Big5_HKSCS";
    }

    public CharToByteBig5_HKSCS() {
        super(enc);
    }
}
