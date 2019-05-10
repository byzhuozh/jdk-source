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

public class ByteToCharCp949C extends ByteToCharDBCS_ASCII {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp949C";
    }

    public ByteToCharCp949C() {
        super((DoubleByte.Decoder)new IBM949C().newDecoder());
    }
}
