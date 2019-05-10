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

public class MS50220 extends ISO2022_JP
{
    public MS50220() {
        super("x-windows-50220",
              ExtendedCharsets.aliasesFor("x-windows-50220"));
    }

    public String historicalName() {
        return "MS50220";
    }

    public boolean contains(Charset cs) {
      return super.contains(cs) ||
             (cs instanceof JIS_X_0212) ||
             (cs instanceof MS50220);
    }

    protected short[] getDecIndex1() {
        return JIS_X_0208_MS5022X_Decoder.index1;
    }

    protected String[] getDecIndex2() {
        return JIS_X_0208_MS5022X_Decoder.index2;
    }

    protected DoubleByteDecoder get0212Decoder() {
        return new JIS_X_0212_MS5022X_Decoder(this);
    }

    protected short[] getEncIndex1() {
        return JIS_X_0208_MS5022X_Encoder.index1;
    }

    protected String[] getEncIndex2() {
        return JIS_X_0208_MS5022X_Encoder.index2;
    }

    protected DoubleByteEncoder get0212Encoder() {
        return new JIS_X_0212_MS5022X_Encoder(this);
    }

    protected boolean doSBKANA() {
        return false;
    }
}
