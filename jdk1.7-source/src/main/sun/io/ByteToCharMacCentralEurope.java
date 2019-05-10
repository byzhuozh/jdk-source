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

import sun.nio.cs.ext.MacCentralEurope;

/**
 * A table to convert to MacCentralEurope to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharMacCentralEurope extends ByteToCharSingleByte {

    private final static MacCentralEurope nioCoder = new MacCentralEurope();

    public String getCharacterEncoding() {
        return "MacCentralEurope";
    }

    public ByteToCharMacCentralEurope() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
