/*
 * Copyright (c) 1996, 2005, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.IBM866;

/**
 * A table to convert to Cp866 to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharCp866 extends ByteToCharSingleByte {

    private final static IBM866 nioCoder = new IBM866();

    public String getCharacterEncoding() {
        return "Cp866";
    }

    public ByteToCharCp866() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
