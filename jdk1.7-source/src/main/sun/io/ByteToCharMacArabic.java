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

import sun.nio.cs.ext.MacArabic;

/**
 * A table to convert to MacArabic to Unicode
 *
 * @author  ConverterGenerator tool
 */

public class ByteToCharMacArabic extends ByteToCharSingleByte {

    private final static MacArabic nioCoder = new MacArabic();

    public String getCharacterEncoding() {
        return "MacArabic";
    }

    public ByteToCharMacArabic() {
        super.byteToCharTable = nioCoder.getDecoderSingleByteMappings();
    }
}
