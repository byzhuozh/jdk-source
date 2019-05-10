/*
 * Copyright (c) 1998, 2010, Oracle and/or its affiliates. All rights reserved.
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

package sun.tools.native2ascii.resources;

import java.util.ListResourceBundle;

public class MsgNative2ascii extends ListResourceBundle {

    public Object[][] getContents() {
        Object[][] temp = new Object[][] {
        {"err.bad.arg", "-encoding requires argument"},
        {"err.cannot.read",  "{0} could not be read."},
        {"err.cannot.write", "{0} could not be written."},
        {"usage", "Usage: native2ascii" +
         " [-reverse] [-encoding encoding] [inputfile [outputfile]]"},
        };

        return temp;
    }
}
