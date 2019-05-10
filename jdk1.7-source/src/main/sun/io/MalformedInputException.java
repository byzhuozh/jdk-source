/*
 * Copyright (c) 1996, 2007, Oracle and/or its affiliates. All rights reserved.
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


/**
* The input string or input byte array to a character conversion
* contains a malformed sequence of characters or bytes.
*
* @author Asmus Freytag
*
* @deprecated Replaced by {@link java.nio.charset}.  THIS API WILL BE
* REMOVED IN J2SE 1.6.
*/
@Deprecated
public class MalformedInputException
    extends java.io.CharConversionException
{
    private static final long serialVersionUID = 2585413228493157652L;

    /**
     * Constructs a MalformedInputException with no detail message.
     * A detail message is a String that describes this particular exception.
     */
    public MalformedInputException() {
        super();
    }

    /**
     * Constructs a MalformedInputException with the specified detail message.
     * A detail message is a String that describes this particular exception.
     * @param s the String containing a detail message
     */
    public MalformedInputException(String s) {
        super(s);
    }
}
