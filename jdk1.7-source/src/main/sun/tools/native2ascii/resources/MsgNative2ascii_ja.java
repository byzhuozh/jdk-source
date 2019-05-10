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

public class MsgNative2ascii_ja extends ListResourceBundle {

    public Object[][] getContents() {
        Object[][] temp = new Object[][] {
        {"err.bad.arg", "-encoding\u306B\u306F\u5F15\u6570\u304C\u5FC5\u8981\u3067\u3059"},
        {"err.cannot.read",  "{0}\u3092\u8AAD\u307F\u8FBC\u3081\u307E\u305B\u3093\u3067\u3057\u305F\u3002"},
        {"err.cannot.write", "{0}\u3092\u66F8\u304D\u8FBC\u3081\u307E\u305B\u3093\u3067\u3057\u305F\u3002"},
        {"usage", "\u4F7F\u7528\u65B9\u6CD5: native2ascii [-reverse] [-encoding encoding] [inputfile [outputfile]]"},
        };

        return temp;
    }
}
