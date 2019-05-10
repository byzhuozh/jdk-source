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

public class ByteToCharCp970 extends ByteToCharEUC2 {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp970";
    }

    public ByteToCharCp970() {
        super((DoubleByte.Decoder)new IBM970().newDecoder());
    }
}
