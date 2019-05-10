/*
 * Copyright (c) 1996, 2002, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.IBM850;

/**
 * A table to convert to Cp850 to Unicode
 *
 * @author  ConverterGenerator tool
 * @version >= JDK1.1.6
 */

public class ByteToCharCp850 extends ByteToCharSingleByte {

    public String getCharacterEncoding() {
        return "Cp850";
    }

    public ByteToCharCp850() {
        super.byteToCharTable = new IBM850().getDecoderSingleByteMappings();
    }
}
