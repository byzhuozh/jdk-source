/*
 * Copyright (c) 1997, Oracle and/or its affiliates. All rights reserved.
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

public class ByteToCharCp942C extends ByteToCharDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp942C";
    }

    public ByteToCharCp942C() {
        super((DoubleByte.Decoder)new IBM942C().newDecoder());
    }
}
