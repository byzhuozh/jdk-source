/*
 * Copyright (c) 1996, Oracle and/or its affiliates. All rights reserved.
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

package sun.applet;

/**
 * An applet security exception.
 *
 * @author      Arthur van Hoff
 */
public
class AppletIllegalArgumentException extends IllegalArgumentException {
    private String key = null;

    public AppletIllegalArgumentException(String key) {
        super(key);
        this.key = key;

    }

    public String getLocalizedMessage() {
        return amh.getMessage(key);
    }

    private static AppletMessageHandler amh = new AppletMessageHandler("appletillegalargumentexception");
}
