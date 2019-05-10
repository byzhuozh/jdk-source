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

import sun.nio.cs.ext.JIS_X_0208_Encoder;

/**
 * Tables and data to convert Unicode to JIS0208
 *
 * @author  ConverterGenerator tool
 */

public class CharToByteJIS0208 extends CharToByteDoubleByte {

    public String getCharacterEncoding() {
        return "JIS0208";
    }

    public CharToByteJIS0208() {
        super.index1 = JIS_X_0208_Encoder.getIndex1();
        super.index2 = JIS_X_0208_Encoder.getIndex2();
    }
}
