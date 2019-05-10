/*
 * Copyright (c) 2005, Oracle and/or its affiliates. All rights reserved.
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

package sun.nio.cs.ext;

import java.nio.charset.Charset;

public class MSISO2022JP extends ISO2022_JP
{
    public MSISO2022JP() {
        super("x-windows-iso2022jp",
              ExtendedCharsets.aliasesFor("x-windows-iso2022jp"));
    }

    public String historicalName() {
        return "windows-iso2022jp";
    }

    public boolean contains(Charset cs) {
      return super.contains(cs) ||
             (cs instanceof MSISO2022JP);
    }

    protected short[] getDecIndex1() {
        return JIS_X_0208_MS932_Decoder.index1;
    }

    protected String[] getDecIndex2() {
        return JIS_X_0208_MS932_Decoder.index2;
    }

    protected DoubleByteDecoder get0212Decoder() {
        return null;
    }

    protected short[] getEncIndex1() {
        return JIS_X_0208_MS932_Encoder.index1;
    }

    protected String[] getEncIndex2() {
        return JIS_X_0208_MS932_Encoder.index2;
    }

    protected DoubleByteEncoder get0212Encoder() {
        return null;
    }

    protected boolean doSBKANA() {
        return true;
    }
}
