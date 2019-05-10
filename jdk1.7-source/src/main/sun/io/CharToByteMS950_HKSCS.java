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

import sun.nio.cs.ext.DoubleByte;
import sun.nio.cs.ext.MS950_HKSCS;

public class CharToByteMS950_HKSCS extends CharToByteDBCS_ASCII {

    private static DoubleByte.Encoder enc =
        (DoubleByte.Encoder)new MS950_HKSCS().newEncoder();

    public String getCharacterEncoding() {
        return "MS950_HKSCS";
    }

    public CharToByteMS950_HKSCS() {
        super(enc);
    }
}
