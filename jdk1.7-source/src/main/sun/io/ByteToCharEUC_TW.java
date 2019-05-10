/*
 * Copyright (c) 1996, 2004, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.EUC_TW;

/*
 * @author Limin Shi
 */
public class ByteToCharEUC_TW extends ByteToCharConverter
{
    private final byte G0 = 0;
    private final byte G1 = 1;
    private final byte G2 = 2;
    private final byte G3 = 3;
    private final byte G4 = 4;
    private final byte MSB = (byte) 0x80;
    private final byte SS2 = (byte) 0x8E;

    private byte firstByte = 0, state = G0;
    private int cnsPlane = 0;

    private EUC_TW.Decoder dec = (EUC_TW.Decoder)(new EUC_TW().newDecoder());

    public ByteToCharEUC_TW() {
    }

    public int flush(char[] output, int outStart, int outEnd)
        throws MalformedInputException
    {
        if (state != G0) {
            state = G0;
            firstByte = 0;
            badInputLength = 0;
            throw new MalformedInputException();
        }
        reset();
        return 0;
    }

    public void reset() {
        dec.reset();
        state = G0;
        firstByte = 0;
        byteOff = charOff = 0;
    }

    /**
     * Character conversion
     */
    public int convert(byte[] input, int inOff, int inEnd,
                       char[] output, int outOff, int outEnd)
        throws UnknownCharacterException, MalformedInputException,
               ConversionBufferFullException
    {
        int inputSize = 0;
        char[] c1 = new char[1];

        byteOff = inOff;
        charOff = outOff;

        cnsPlane = 3;
        while (byteOff < inEnd) {
            if (charOff >= outEnd)
                throw new ConversionBufferFullException();
            char[] outputChar = null;
            switch (state) {
            case G0:
                if ( (input[byteOff] & MSB) == 0) {     // ASCII
                    outputChar = c1;
                    outputChar[0] = (char) input[byteOff];
                } else if (input[byteOff] == SS2) {     // Codeset 2
                    state = G2;
                } else {                                // Codeset 1
                    firstByte = input[byteOff];
                    state = G1;
                }
                break;
            case G1:
                inputSize = 2;
                if ( (input[byteOff] & MSB) != 0) {     // 2nd byte
                    cnsPlane = 0;
                    outputChar = dec.toUnicode(firstByte & 0xff,
                                               input[byteOff] & 0xff,
                                               cnsPlane);
                } else {                                // Error
                    badInputLength = 1;
                    throw new MalformedInputException();
                }
                firstByte = 0;
                state = G0;
                break;
            case G2:
                cnsPlane = (input[byteOff] & (byte)0x0f);
                // Adjust String array index for plan 15
                cnsPlane = (cnsPlane == 15)? 8 : cnsPlane;

                if (cnsPlane < 15) {
                     state = G3;
                } else {
                    badInputLength = 2;
                    throw new MalformedInputException();
                }

                break;
            case G3:
                if ( (input[byteOff] & MSB) != 0) {     // 1st byte
                    firstByte = input[byteOff];
                    state = G4;
                } else {                                // Error
                    state = G0;
                    badInputLength = 2;
                    throw new MalformedInputException();
                }
                break;
            case G4:
                if ( (input[byteOff] & MSB) != 0) {     // 2nd byte
                    outputChar = dec.toUnicode(firstByte & 0xff,
                                               input[byteOff] & 0xff,
                                               cnsPlane - 1);
                } else {                                // Error
                    badInputLength = 3;
                    throw new MalformedInputException();
                }
                firstByte = 0;
                state = G0;
                break;
            }
            byteOff++;
            if (state == G0) {
                if (outputChar == null) {
                    if (subMode) {               // substitution enabled
                        outputChar = c1;
                        outputChar[0] = subChars[0];
                    } else {
                        badInputLength = inputSize;
                        throw new UnknownCharacterException();
                    }
                }
                output[charOff++] = outputChar[0];
            }
        }
        return charOff - outOff;
    }


    /**
     * Return the character set ID
     */
    public String getCharacterEncoding() {
        return "EUC_TW";
    }
}
