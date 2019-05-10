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

public class ByteToCharCp942 extends ByteToCharDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp942";
    }

    public ByteToCharCp942() {
        super((DoubleByte.Decoder)new IBM942().newDecoder());
    }
}
