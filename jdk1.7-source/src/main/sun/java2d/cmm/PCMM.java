/*
 * Copyright (c) 2006, Oracle and/or its affiliates. All rights reserved.
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

package sun.java2d.cmm;

import java.awt.color.ICC_Profile;

/* Pluggable CMM interface */

public interface PCMM {

    /* methods invoked from ICC_Profile */
    public long loadProfile(byte[] data);
    public void freeProfile(long profileID);
    public int  getProfileSize(long profileID);
    public void getProfileData(long profileID, byte[] data);
    public void getTagData(long profileID, int tagSignature, byte[] data);
    public int getTagSize(long profileID, int tagSignature);
    public void setTagData(long profileID, int tagSignature, byte[] data);

    /* methods for creating ColorTransforms */
    public ColorTransform createTransform(ICC_Profile profile, int renderType,
                                          int transformType);

    public ColorTransform createTransform(ColorTransform[] transforms);
}
