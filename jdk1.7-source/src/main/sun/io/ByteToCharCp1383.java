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

public class ByteToCharCp1383 extends ByteToCharEUC2 {

    // Return the character set id
    public String getCharacterEncoding() {
        return "Cp1383";
    }

    public ByteToCharCp1383() {
        super((DoubleByte.Decoder)new IBM1383().newDecoder());
    }
}
