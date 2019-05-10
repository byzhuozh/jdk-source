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

public class ByteToCharCp933 extends ByteToCharDBCS_EBCDIC {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp933";
    }

    public ByteToCharCp933() {
        super((DoubleByte.Decoder)new IBM933().newDecoder());
    }
}
