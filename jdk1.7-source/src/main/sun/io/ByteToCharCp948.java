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

public class ByteToCharCp948 extends ByteToCharDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp948";
    }

    public ByteToCharCp948() {
        super((DoubleByte.Decoder)new IBM948().newDecoder());
    }
}
