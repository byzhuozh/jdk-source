/*
 * Copyright (c) 1996, 2003, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.MacGreek;

/**
 * A table to convert to MacGreek to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharMacGreek extends ByteToCharSingleByte {

    private final static MacGreek nioCoder = new MacGreek();

    public String getCharacterEncoding() {
        return "MacGreek";
    }

    public ByteToCharMacGreek() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
